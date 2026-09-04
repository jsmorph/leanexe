#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-variable"
#endif
#define main lanyon_upstream_placeholder_main
#include "lanyon/a736aa5f8b17efd225c4692404e2442361d06729/compressible_euler_1d.c"
#undef main
#if defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

static const char adapter_name[] = "verified-dyadic-conservative-v1";

static int
supported_binary64_environment(void)
{
  const double one = 1.0;
  uint64_t one_bits;
#if !defined(__STDC_IEC_559__)
  fprintf(stderr, "lanyon-driver: C implementation does not advertise IEC 60559 arithmetic\n");
  return 0;
#endif
  if (CHAR_BIT != 8 || sizeof(uint64_t) != 8 || sizeof(double) != 8 ||
      FLT_RADIX != 2 || DBL_MANT_DIG != 53 || DBL_MAX_EXP != 1024 ||
      DBL_MIN_EXP != -1021 || FLT_EVAL_METHOD != 0) {
    fprintf(stderr, "lanyon-driver: unsupported binary64 platform\n");
    return 0;
  }
  memcpy(&one_bits, &one, sizeof(one_bits));
  if (one_bits != UINT64_C(0x3ff0000000000000)) {
    fprintf(stderr, "lanyon-driver: unsupported binary64 word layout\n");
    return 0;
  }
  if (fesetround(FE_TONEAREST) != 0 || fegetround() != FE_TONEAREST) {
    fprintf(stderr, "lanyon-driver: round-to-nearest mode is unavailable\n");
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

static double
binary64_sub(double left, double right)
{
  volatile double result = left - right;
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

static compressible_euler_1d_state
verified_dyadic_conservative(uint64_t rho_bits, uint64_t u_bits,
                             uint64_t p_bits)
{
  const double half = double_from_bits(UINT64_C(0x3fe0000000000000));
  const double rho = double_from_bits(rho_bits);
  const double u = double_from_bits(u_bits);
  const double pressure = double_from_bits(p_bits);
  const double momentum = binary64_mul(rho, u);
  const double velocity_squared_mass = binary64_mul(momentum, u);
  const double half_kinetic = binary64_mul(half, velocity_squared_mass);
  const double half_pressure = binary64_mul(half, pressure);
  const double two_pressure = binary64_add(pressure, pressure);
  const double energy_pressure = binary64_add(two_pressure, half_pressure);
  const double energy = binary64_add(energy_pressure, half_kinetic);
  compressible_euler_1d_state state = { rho, momentum, energy };
  return state;
}

static void
print_word(double value)
{
  printf("%016" PRIx64, bits_from_double(value));
}

int
main(int argc, char **argv)
{
  uint64_t words[6];
  compressible_euler_1d_coordinates coordinate_l;
  compressible_euler_1d_coordinates coordinate_r;
  compressible_euler_1d_parameters parameters;
  compressible_euler_1d_state state_l;
  compressible_euler_1d_state state_r;
  compressible_euler_1d_flux physical_l;
  compressible_euler_1d_flux physical_r;
  compressible_euler_1d_lax_friedrichs_speed_family speeds;
  compressible_euler_1d_lax_friedrichs_fluctuation fluctuation_l;
  compressible_euler_1d_lax_friedrichs_fluctuation fluctuation_r;
  compressible_euler_1d_flux numerical_from_l;
  compressible_euler_1d_flux numerical_from_r;
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
      fprintf(stderr, "lanyon-driver: argument %d is not a lowercase 16-hex word\n", index + 1);
      return 2;
    }
  }
  if (!raw_guard(words[0], words[1], words[2],
                 words[3], words[4], words[5])) {
    fprintf(stderr,
        "lanyon-driver: %s refuses inputs rejected by the verified raw guard\n",
        adapter_name);
    return 2;
  }

  coordinate_l.x = 0.0;
  coordinate_r.x = 0.0;
  parameters.gas_gamma = 7.0 / 5.0;
  if (bits_from_double(parameters.gas_gamma) != UINT64_C(0x3ff6666666666666)) {
    fprintf(stderr, "lanyon-driver: C gamma expression has an unexpected binary64 word\n");
    return 2;
  }
  state_l = verified_dyadic_conservative(words[0], words[1], words[2]);
  state_r = verified_dyadic_conservative(words[3], words[4], words[5]);

  compressible_euler_1d_x_flux(&coordinate_l, &parameters, &state_l, &physical_l);
  compressible_euler_1d_x_flux(&coordinate_r, &parameters, &state_r, &physical_r);
  compressible_euler_1d_lax_friedrichs_x_speed_family(
      &coordinate_l, &coordinate_r, &state_l, &state_r, &parameters, &speeds);
  compressible_euler_1d_lax_friedrichs_x_left_fluctuation(
      &coordinate_l, &coordinate_r, &state_l, &state_r, &parameters,
      &fluctuation_l);
  compressible_euler_1d_lax_friedrichs_x_right_fluctuation(
      &coordinate_l, &coordinate_r, &state_l, &state_r, &parameters,
      &fluctuation_r);

  numerical_from_l.flux_rho = binary64_add(physical_l.flux_rho, fluctuation_l.fluctuation_rho);
  numerical_from_l.flux_mom = binary64_add(physical_l.flux_mom, fluctuation_l.fluctuation_mom);
  numerical_from_l.flux_energy = binary64_add(physical_l.flux_energy, fluctuation_l.fluctuation_energy);
  numerical_from_r.flux_rho = binary64_sub(physical_r.flux_rho, fluctuation_r.fluctuation_rho);
  numerical_from_r.flux_mom = binary64_sub(physical_r.flux_mom, fluctuation_r.fluctuation_mom);
  numerical_from_r.flux_energy = binary64_sub(physical_r.flux_energy, fluctuation_r.fluctuation_energy);

  print_word(state_l.rho);
  putchar(',');
  print_word(state_l.mom);
  putchar(',');
  print_word(state_l.energy);
  putchar(',');
  print_word(state_r.rho);
  putchar(',');
  print_word(state_r.mom);
  putchar(',');
  print_word(state_r.energy);
  putchar(',');
  print_word(speeds.speed2);
  putchar(',');
  print_word(numerical_from_l.flux_rho);
  putchar(',');
  print_word(numerical_from_l.flux_mom);
  putchar(',');
  print_word(numerical_from_l.flux_energy);
  putchar(',');
  print_word(numerical_from_r.flux_rho);
  putchar(',');
  print_word(numerical_from_r.flux_mom);
  putchar(',');
  print_word(numerical_from_r.flux_energy);
  putchar('\n');
  return 0;
}
