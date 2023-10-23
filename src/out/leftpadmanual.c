#include "stdlib.h"

/*@ requires \valid(src + (0..l-1));
    requires \valid(dst + (0..n-1));
    requires \separated(src+(0..l-1), dst+(0..n-1)) && n >= l;

    ensures \let p = n-l; \forall integer i; (
      (0 <= i < p ==> dst[i] == c) &&
      (p <= i < n ==> dst[i] == src[i-p]));
    assigns dst[0..n];
 */
void leftpad(int c, int *src, size_t l, int *dst, size_t n) {
  size_t p = n - l;

  /*@ loop assigns x, dst[p..n];
      loop invariant x_range_1: 0 <= x <= l;
      loop invariant dst_copy: \forall integer i; 0 <= i < x ==> dst[i+p] == src[i];
      loop variant l-x;
   */
  for (size_t x = 0; x < l; x++) {
    dst[x+p] = src[x];
  }

  /*@ loop assigns x, dst[0..p-1];
      loop invariant x_range_2: 0 <= x <= p;
      loop invariant dst_pad: \forall integer i; 0 <= i < x ==> dst[i] == c;
      loop variant p-x;
   */
  for (size_t x = 0; x < p; x++) {
    dst[x] = c;
  }
}
