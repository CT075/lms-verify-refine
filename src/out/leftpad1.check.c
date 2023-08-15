#include <limits.h>
/*@ predicate eq_Int(int  x0, int  x1) = (x0==x1);*/
/*@
assigns \nothing;
ensures \result <==> eq_Int(x0, x1);
*/
int eq_Int(int  x0, int  x1) {
  int x3 = x0 == x1;
  return x3;
}
/*@ predicate inv_vec_Int(int  * x4, integer  x5) = ((x5==0) || ((x5>0) &&
\valid(x4+(0..x5-1))));*/
/*@
requires (inv_vec_Int(x20,x21) &&
inv_vec_Int(x22,x23));
ensures (inv_vec_Int(x20,x21) &&
inv_vec_Int(x22,x23));
*/
void leftpad(int  x19, int  * x20, int  x21, int  * x22, int  x23) {
  int x25 = x23 > x21;
  if (x25) {
    int x26 = x23 - x21;
    /*@
    loop invariant 0<=x28<=x21;
    loop assigns x28, x22[(x26..x23-1)];
    loop variant x21-x28;
    */
    for(int x28=0; x28 < x21; x28++) {
      int x33 = x26 + x28;
      int x34 = x20[x28];
      x22[x33] = x34;
    }
    int x53 = x26 - 1;
    /*@
    loop invariant 0<=x39<=x26;
    loop invariant (\forall int  x44; (((0<=x44) &&
    (x44<(x39-1))) ==> eq_Int(x22[x44],x19)));
    loop assigns x39, x22[(0..x26-1)];
    loop variant x26-x39;
    */
    for(int x39=0; x39 < x26; x39++) {
      int x54 = x53 - x39;
      x22[x54] = x19;
    }
  } else {
  }
}
