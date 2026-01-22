#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
/*
 * Standalone tutorial C library for WolframEngine ↔ C ForeignFunctionLoad demos.
 *
 * NOTE: This is intentionally NOT part of the repo-integrated Lean→C export workflow.
 * The real integration uses dist/lambda_kernel_export/libheyting_kernel.so produced by
 * `lake exe lambda_kernel_export` and exercised by scripts/qa_wolfram_bridge.sh.
 */
/*
 * BASIC INTEGER ARITHMETIC
 * (placeholders for Lean-verified arithmetic)
 */
uint64_t verified_field_add(uint64_t a, uint64_t b) { return a + b; }

uint64_t verified_field_mult(uint64_t a, uint64_t b) { return a * b; }

uint64_t verified_mod_exp(uint64_t base, uint64_t exp, uint64_t mod) {
  if (mod == 0) {
    return 0;
  }
  uint64_t result = 1;
  base = base % mod;
  while (exp > 0) {
    if ((exp & 1u) == 1u) {
      result = (result * base) % mod;
    }
    exp >>= 1u;
    base = (base * base) % mod;
  }
  return result;
}

/*
 * ARRAY/BUFFER FUNCTIONS
 */
double sum_array(const double* arr, int64_t len) {
  if (arr == NULL || len <= 0) {
    return 0.0;
  }
  double sum = 0.0;
  for (int64_t i = 0; i < len; i++) {
    sum += arr[i];
  }
  return sum;
}

double dot_product(const double* a, const double* b, int64_t len) {
  if (a == NULL || b == NULL || len <= 0) {
    return 0.0;
  }
  double result = 0.0;
  for (int64_t i = 0; i < len; i++) {
    result += a[i] * b[i];
  }
  return result;
}

void scale_array(double* arr, int64_t len, double scalar) {
  if (arr == NULL || len <= 0) {
    return;
  }
  for (int64_t i = 0; i < len; i++) {
    arr[i] *= scalar;
  }
}

double* create_sequence(int64_t n, double start, double step) {
  if (n <= 0) {
    return NULL;
  }
  if ((uint64_t)n > (SIZE_MAX / sizeof(double))) {
    return NULL;
  }
  double* arr = (double*)malloc((size_t)n * sizeof(double));
  if (arr == NULL) {
    return NULL;
  }
  for (int64_t i = 0; i < n; i++) {
    arr[i] = start + (double)i * step;
  }
  return arr;
}

void free_array(double* arr) { free(arr); }

/*
 * STRUCT-BASED FUNCTIONS
 */
typedef struct {
  double real;
  double imag;
} Complex;

Complex complex_mult(Complex a, Complex b) {
  Complex result;
  result.real = a.real * b.real - a.imag * b.imag;
  result.imag = a.real * b.imag + a.imag * b.real;
  return result;
}

double complex_magnitude(Complex c) { return sqrt(c.real * c.real + c.imag * c.imag); }

/*
 * BYTE-STRING FUNCTIONS
 *
 * ForeignFunctionLoad does not expose a stable "CString" parameter type for direct
 * string passing in our usage; instead we pass a pointer + explicit length.
 */
int64_t string_length(const uint8_t* bytes, int64_t len) {
  if (bytes == NULL || len < 0) {
    return 0;
  }
  return len;
}

int32_t is_palindrome(const uint8_t* bytes, int64_t len) {
  if (bytes == NULL || len <= 1) {
    return 1;
  }
  int64_t i = 0;
  int64_t j = len - 1;
  while (i < j) {
    if (bytes[i] != bytes[j]) {
      return 0;
    }
    i++;
    j--;
  }
  return 1;
}

/*
 * STATE FUNCTIONS
 */
static uint64_t call_counter = 0;

uint64_t get_call_count(void) { return call_counter; }

void increment_counter(void) { call_counter++; }

void reset_counter(void) { call_counter = 0; }

/*
 * ERROR HANDLING SIMULATION
 */
int32_t safe_divide(double a, double b, double* result) {
  if (result == NULL) {
    return -2;
  }
  if (b == 0.0) {
    return -1;
  }
  *result = a / b;
  return 0;
}

