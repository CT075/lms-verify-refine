#include "stdlib.h"

/*@ requires \valid(src + (0..l)) && \valid(dst + (0..n));

    ensures \let p = n-l; \forall integer i; ((0 <= i < p ==> dst[i] == c) && (p <= i < n ==> dst[i] == src[i-p]));
    assigns dst[0..n];
 */
void leftpad(int c, int *src, size_t l, int *dst, size_t n) {
  if (n > l) {
    size_t p = n - l;

    /*@ loop assigns x, dst[p..n];
        loop invariant x_range_1: 0 <= x <= l;
        loop invariant dst_copy: \forall integer i; 0 <= i < x ==> dst[i+p] == src[i];
        loop variant l-x;
     */
    for (size_t x = 0; x < l; x++) {
      //@ assert loop_inv_entry: \forall integer i; 0 <= i < x ==> dst[i+p] == src[i];
      dst[x+p] = src[x];
      // Cam: I don't understand why it can't prove this.
      //@ assert prev_loop_inv_after_assign: \forall integer i; 0 <= i < x ==> dst[i+p] == src[i];
    }

    //@ assert dst_copy_all: \forall integer i; p <= i < n ==> dst[i] == src[i-p];

    /*@ loop assigns x, dst[0..p];
        loop invariant x_range_2: 0 <= x <= p;
        loop invariant dst_pad: \forall integer i; 0 <= i < x ==> dst[i] == c;
        loop variant p-x;
     */
    for (size_t x = 0; x < p; x++) {
      dst[x] = c;
    }

    //@ assert dst_pad_all: \forall integer i; 0 <= i < p ==> dst[i] == c;
  }
}
