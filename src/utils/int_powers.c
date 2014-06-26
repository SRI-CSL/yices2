#include "utils/int_powers.h"

uint32_t upower32(uint32_t x, uint32_t d) {
  uint32_t y;

  y = 1;
  while (d != 0) {
    if ((d & 1) != 0) {
      y *= x;
    }
    d >>= 1;
    x *= x;
  }
  return y;
}


uint64_t upower64(uint64_t x, uint32_t d) {
  uint64_t y;

  y = 1;
  while (d != 0) {
    if ((d & 1) != 0) {
      y *= x;
    }
    d >>= 1;
    x *= x;
  }
  return y;
}
